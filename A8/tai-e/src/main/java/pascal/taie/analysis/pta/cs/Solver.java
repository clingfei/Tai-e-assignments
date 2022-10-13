/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    private final Map<Var, Set<Invoke>> argInvokeMap;
    private final Map<Invoke, Set<Var>> invokeBaseObjMap;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
        this.argInvokeMap = new HashMap<>();
        this.invokeBaseObjMap = new HashMap<>();
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            //Context context = csMethod.getContext();
            JMethod jMethod = csMethod.getMethod();
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            for (Stmt stmt : jMethod.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    public void workListAddEntry(CSVar ptr, CSObj csObj) {
        if (ptr != null && csObj != null)
            workList.addEntry(ptr, PointsToSetFactory.make(csObj));
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);
            CSVar x = csManager.getCSVar(context, stmt.getLValue());

            Context ctx = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(ctx, obj);
            PointsToSet pointsToSet = PointsToSetFactory.make(csObj);
            workList.addEntry(x, pointsToSet);
            return null;
        }

        public Void visit(Copy stmt) {
            CSVar source = csManager.getCSVar(context, stmt.getRValue());
            CSVar target = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(source, target);
            return null;
        }
        // y = x.f
        public Void visit(LoadField stmt) {
            if (!stmt.isStatic()) return null;
            StaticField source = csManager.getStaticField(stmt.getFieldRef().resolve());
            CSVar target = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(source, target);
            return null;
        }

        // x.f = y.
        public Void visit(StoreField stmt) {
            if (!stmt.isStatic()) return null;
            CSVar source = csManager.getCSVar(context, stmt.getRValue());
            StaticField target = csManager.getStaticField(stmt.getFieldRef().resolve());
            addPFGEdge(source, target);
            return null;
        }

        public Void visit(Invoke stmt) {
            for (Var var: stmt.getInvokeExp().getArgs()) {
                argInvokeMap.computeIfAbsent(var, (k) -> new HashSet<>());
                Set<Invoke> argInvokeSet = argInvokeMap.get(var);
                argInvokeSet.add(stmt);
            }
            if (!stmt.isStatic()) return null;
            processInstStaticCall(null, stmt, context, null);
            // source只有静态调用
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target))
            if (!source.getPointsToSet().isEmpty())
                workList.addEntry(target, source.getPointsToSet());
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer(), entry.pointsToSet());
            if (entry.pointer() instanceof CSVar varPtr) {
                Var x = varPtr.getVar();
                // c
                Context context = varPtr.getContext();
                for (var obj : delta.getObjects()) {
                    // y = x.f
                    for (var loadField : x.getLoadFields()) {
                        if (loadField.isStatic()) continue;
                        addPFGEdge(
                                csManager.getInstanceField(obj, loadField.getFieldRef().resolve()),
                                csManager.getCSVar(context, loadField.getLValue())
                        );
                    }
                    // x.f = y
                    for (var storeField : x.getStoreFields()) {
                        if (storeField.isStatic()) continue;
                        addPFGEdge(
                                csManager.getCSVar(context, storeField.getRValue()) ,
                                csManager.getInstanceField(obj, storeField.getFieldRef().resolve())
                        );
                    }
                    //y = x[i]
                    for (var loadArray : x.getLoadArrays()) {
                        addPFGEdge(
                                csManager.getArrayIndex(obj),
                                csManager.getCSVar(context, loadArray.getLValue())
                        );
                    }
                    // x[i] = y
                    for (var storeArray : x.getStoreArrays()) {
                        addPFGEdge(
                                csManager.getCSVar(context, storeArray.getRValue()),
                                csManager.getArrayIndex(obj)
                        );
                    }
                    processCall((CSVar) entry.pointer(), obj);
                }
                argInvokeMap.computeIfAbsent(x, (k) -> new HashSet<>());
                for (Invoke argInvoke: argInvokeMap.get(x)) {
                    Var resultVar = argInvoke.getLValue();
                    invokeBaseObjMap.computeIfAbsent(argInvoke, (k) -> new HashSet<>());
                    for (Var recvVar: invokeBaseObjMap.get(argInvoke)) {
                        taintAnalysis.processTransfer(context, recvVar, resultVar, argInvoke);
                    }
                    taintAnalysis.processTransfer(context, null, resultVar, argInvoke);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = PointsToSetFactory.make();
        if (!pointsToSet.isEmpty()) {
            PointsToSet ptn = pointer.getPointsToSet();
            for (var obj : pointsToSet)
                if (!ptn.contains(obj))
                    delta.addObject(obj);
            ptn.addAll(delta);
            if (!delta.isEmpty())
                for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer))
                    workList.addEntry(succ, delta);
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        if (recv == null) return;
        for (var invoke : recv.getVar().getInvokes()) {
            invokeBaseObjMap.computeIfAbsent(invoke, (k) -> new HashSet<>());
            invokeBaseObjMap.get(invoke).add(recv.getVar());
            processInstStaticCall(recvObj, invoke, recv.getContext(), recv);
        }
    }

    private void processInstStaticCall(CSObj recv, Invoke stmt, Context context, CSVar recvVar) {
        JMethod jMethod = resolveCallee(recv, stmt);
        //if (jMethod == null) return;
        // callSite应该是与stmt保持一致
        CSCallSite callSite = csManager.getCSCallSite(context, stmt);
        Context callCtx = contextSelector.selectContext(callSite, recv, jMethod);
        // 但是CSMethod应该通过select选择context？
        CSMethod csMethod = csManager.getCSMethod(callCtx, jMethod);
        if (recv != null)
            workList.addEntry(csManager.getCSVar(callCtx, jMethod.getIR().getThis()), PointsToSetFactory.make(recv));
        if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), callSite, csMethod))) {
            addReachable(csMethod);
            // 形参
            List<Var> params = jMethod.getIR().getParams();
            // 实参
            List<Var> args = stmt.getInvokeExp().getArgs();
            assert args.size() == params.size();
            for (int i = 0; i < args.size(); i++) {
                addPFGEdge(
                        csManager.getCSVar(context, args.get(i)),
                        csManager.getCSVar(callCtx, params.get(i))
                );
            }
            List<Var> retVars = jMethod.getIR().getReturnVars();
            Var result = stmt.getResult();
            if (result != null) {
                CSVar csResult = csManager.getCSVar(context, result);
                for (var retVar : retVars) {
                    addPFGEdge(
                            csManager.getCSVar(callCtx, retVar),
                            csResult
                    );
                }
            }
        }
        Set<CSObj> csObj = taintAnalysis.processSource(stmt);
        if (stmt.getLValue() != null) {
            for (var obj : csObj) {
                workList.addEntry(
                        csManager.getCSVar(context, stmt.getLValue()),
                        PointsToSetFactory.make(obj)
                );
            }
        }
        taintAnalysis.processTransfer(context, recvVar != null ? recvVar.getVar() : null, stmt.getLValue(), stmt);
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
