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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me
    public Set<CSObj> processSource(Invoke invoke) {
        Set<CSObj> csObjSet = new HashSet<>();
        for (Source source : config.getSources()) {
            if (source.method() == invoke.getInvokeExp().getMethodRef().resolve() &&
                source.type() == invoke.getInvokeExp().getMethodRef().getReturnType())
                csObjSet.add(csManager.getCSObj(emptyContext, manager.makeTaint(invoke, source.type())));
        }
        return csObjSet;
    }

    public void processTransfer(Context invokeContext, Var recvVar, Var resultVar, Invoke invoke) {
        CSVar csRecvVar = null, csResultVar = null;
        if (recvVar != null) csRecvVar = csManager.getCSVar(invokeContext, recvVar);
        if (resultVar != null) csResultVar = csManager.getCSVar(invokeContext, resultVar);
        for (TaintTransfer transfer: config.getTransfers()) {
            // check whether method equals
            if (Objects.equals(transfer.method(), invoke.getMethodRef().resolve())) {
                // Base to result
                if (transfer.from() == -1 && transfer.to() == -2) {
                    if (csRecvVar != null && csResultVar != null) { // Dynamic Invoke
                        baseToResult(csRecvVar, csResultVar, transfer);
                    }
                }
                // Arg to base
                else if (transfer.from() >= 0 && transfer.to() == -1) {
                    processArg(invokeContext, invoke, csRecvVar, transfer);
                }
                // Arg to result
                else if (transfer.from() >= 0 && transfer.to() == -2) {
                    processArg(invokeContext, invoke, csResultVar, transfer);
                }
                else {
                    throw new AssertionError("Unreachable code path!");
                }
            }
        }
    }

    private void baseToResult(CSVar csRecvVar, CSVar csResultVar, TaintTransfer transfer) {
        for (CSObj csObj: csRecvVar.getPointsToSet().getObjects()) {
            Obj obj = csObj.getObject();
            if (manager.isTaint(obj)) {
                // 通过workList将污点传播出去
                CSObj newTaintObj = csManager.getCSObj(emptyContext,
                        manager.makeTaint(manager.getSourceCall(obj), transfer.type()));
                solver.workListAddEntry(csResultVar, newTaintObj);
            }
        }
    }

    private void processArg(Context invokeContext, Invoke invoke, CSVar csRecvVar, TaintTransfer transfer) {
        if (csRecvVar != null) { // Dynamic Invoke
            CSVar csArgIVar = csManager.getCSVar(invokeContext,
                    invoke.getInvokeExp().getArg(transfer.from()));
            baseToResult(csArgIVar, csRecvVar, transfer);
        }
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        return taintFlows;
    }
}
