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

package pascal.taie.analysis.pta.ci;

import fj.P;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;
import java.util.Set;

import static pascal.taie.analysis.graph.callgraph.CallKind.*;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);
    // 用于对堆抽象进行建模，为每一个allocation site创建与之对应的抽象对象。
    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        // what is RM?
        if (callGraph.addReachableMethod(method)) {
            // How to add new statements?
            // 只需要处理静态字段，而实例字段将在process call和propagate后处理
            IR stmtIR = method.getIR();
            for (var stmt : stmtIR.getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            VarPtr x = pointerFlowGraph.getVarPtr(stmt.getLValue());
            Obj o = heapModel.getObj(stmt);
            PointsToSet newSet = new PointsToSet();
            newSet.addObject(o);
            workList.addEntry(x, newSet);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            VarPtr x = pointerFlowGraph.getVarPtr(stmt.getLValue());
            VarPtr y = pointerFlowGraph.getVarPtr(stmt.getRValue());
            addPFGEdge(y, x);
            return null;
        }

        // what is load ? y = T.f
        @Override
        public Void visit(LoadField stmt) {
            if (!stmt.isStatic()) return null;
            // field is T.f?
            addPFGEdge(
                    pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue())
            );
            return null;
        }

        // what is store ? T.f = y
        @Override
        public Void visit(StoreField stmt) {
            if (!stmt.isStatic()) return null;
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve())
            );
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            /*
             * 静态方法的处理与实例方法大体相同，除了
             * 1）我们不需要在 receiver object 上进行 dispatch 以解析（resolve）出被调用的方法，
             * 2）我们不需要传 receiver object
             */
            // addPfg edge上面没有区别？
            // TODO: 使用resolveCallee解析被调用者，建立调用图
            if (!stmt.isStatic()) return null;
            processInstStaticCall(stmt, null);
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer n = entry.pointer();
            PointsToSet setToPro = propagate(n, entry.pointsToSet());
            if (n instanceof VarPtr) {
                Var x = ((VarPtr) n).getVar();
                for (Obj obj : setToPro.getObjects()) {
                    for (LoadField loadField : x.getLoadFields()) {
                        if (loadField.isStatic()) continue;
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(loadField.getLValue()),
                                pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve())
                        );
                    }
                    for (StoreField storeField : x.getStoreFields()) {
                        if (storeField.isStatic()) continue;
                        addPFGEdge(
                                pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve()),
                                pointerFlowGraph.getVarPtr(storeField.getRValue())
                        );
                    }
                    for (LoadArray loadArray : x.getLoadArrays()) {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(loadArray.getLValue()),
                                pointerFlowGraph.getArrayIndex(obj)
                        );
                    }
                    for (StoreArray storeArray : x.getStoreArrays()) {
                        addPFGEdge(
                                pointerFlowGraph.getArrayIndex(obj),
                                pointerFlowGraph.getVarPtr(storeArray.getRValue())
                        );
                    }
                    processCall(x, obj);
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
        PointsToSet ptn = pointer.getPointsToSet();
        PointsToSet setToPro = new PointsToSet();
        for (Obj obj : pointsToSet)
            if (!ptn.contains(obj))
                setToPro.addObject(obj);
        if (!setToPro.isEmpty()) {
            for (Obj obj : setToPro)
                ptn.addObject(obj);
            for (Pointer succ: pointerFlowGraph.getSuccsOf(pointer))
                workList.addEntry(succ, setToPro);
        }
        return setToPro;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        if (recv == null) return;
        for (Invoke invoke : var.getInvokes()) {
            processInstStaticCall(invoke, recv);
        }
    }

    private void processInstStaticCall(Invoke invoke, Obj recv) {
        JMethod method = resolveCallee(recv, invoke);
        if (recv != null) {
            workList.addEntry(pointerFlowGraph.getVarPtr(method.getIR().getThis()), new PointsToSet(recv));
        }
        if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method))) {
            addReachable(method);
            List<Var> args = invoke.getInvokeExp().getArgs();
            List<Var> params = method.getIR().getParams();
            assert args.size() == params.size();
            for (int i = 0; i < args.size(); i++)
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(args.get(i)),
                        pointerFlowGraph.getVarPtr(params.get(i))
                );
            Var r = invoke.getResult();
            if (r != null) {
                for (Var mret : method.getIR().getReturnVars()) {
                    addPFGEdge(
                            pointerFlowGraph.getVarPtr(mret),
                            pointerFlowGraph.getVarPtr(r)
                    );
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
