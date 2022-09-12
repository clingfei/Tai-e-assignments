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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.List;
import java.util.Optional;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    /*
     * transferEdge(edge, fact) 函数来实现 edge transfer。
     * 它以 ICFG 中的一条边（对应参数 edge）和边的源节点的 OUT fact（对应参数fact）为输入，并输出经transfer计算之后的结果fact。
     */
    // 如果in和out两个一样， 返回true，否则返回false.
    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (!out.equals(in)) {
            out.copyFrom(in);
            return true;
        } else {
            return false;
        }
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        // transferEdge(edge, fact) = fact.
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        /*
         * 对于方法调用 x = m(…)，edge transfer 函数会把等号左侧的变量（在这个例子里也就是 x）和它的值从 fact 中kill 掉。
         * 而对于等号左侧没有变量的调用，比如 m(…)，edge transfer 函数的处理方式与对待 normal edge 的一致：
         * 不修改 fact，edge transfer 是一个恒等函数。
         */
        CPFact entryFact = out.copy();
        Invoke invoke = (Invoke) edge.getSource();
        Var lValue = invoke.getLValue();
        if (lValue != null) {
            entryFact.remove(lValue);
        }
        return entryFact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        /*
         * 对于这种边，edge transfer 函数会将实参（argument）在调用点中的值传递给被调用函数的形参（parameter）。
         * 具体来说，edge transfer 首先从调用点的 OUT fact 中获取实参的值，然后返回一个新的 fact，这个 fact 把形参映射到它对应的实参的值。
         * 举个例子，在图 1 里，transferEdge(2→4, {a=6}) = {x=6}。
         * 此时，edge transfer 函数的返回值应该仅包含被调用函数的形参的值（比如图 1 里，addOne() 的 x）
         */
        // 我可以用getUses中的变脸作为索引从callSiteOut中取出对应的值
        // 但是我应该怎么获得对应的形参列表呢？JMethod?
        // 实际上在传递参数的时候，无论实参是变量、literal、exp or function call，实际上传递的都是一个临时变量
        // 因此实际上我并不需要去再计算变量的值，只需要删除即可
        assert edge.getSource() instanceof Invoke;
        var entryFact = new CPFact();
        Invoke callSite = (Invoke) edge.getSource();
        // 实参列表
        List<Var> argList = callSite.getInvokeExp().getArgs();
        // 形参列表
        List<Var> paramList = edge.getCallee().getIR().getParams();
        /*
         * y = call(1, 2, 3)            argList = {%intconst0, %intconst1, %intconst2} = {1, 2, 3}
         * function call (int x, int y, int z)      paramList = {x, y ,z}
         * 映射是将argList中的变量映射到
         */
        for (int i = 0; i < argList.size(); i++) {
            //
            entryFact.update(paramList.get(i), callSiteOut.get(argList.get(i)));
        }
        return entryFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        /*
         * edge transfer 函数将被调用方法的返回值传递给调用点等号左侧的变量。
         * 具体来说，它从被调用方法的 exit 节点的 OUT fact 中获取返回值（可能有多个，你需要思考一下该怎么处理），
         * 然后返回一个将调用点等号左侧的变量映射到返回值的 fact。举个例子，在图1中，transferEdge(6→3, {x=6,y=7}) = {b=7}。
         * 此时，edge transfer 函数返回的结果应该仅包含调用点等号左侧变量的值（例如图1在第三条语句处的b）。
         * 如果该调用点等号左侧没有变量，那么 edge transfer 函数仅会返回一个空 fact。
         */
        assert edge.getCallSite() instanceof Invoke;
        Var lValue = ((Invoke) edge.getCallSite()).getLValue();
        CPFact returnFact = new CPFact();
        if (lValue != null) {
            Value resultValue = Value.getUndef();
            for (var value : edge.getReturnVars()) {
                resultValue = cp.meetValue(resultValue, returnOut.get(value));
            }
            returnFact.update(lValue, resultValue);
        }
        return returnFact;
    }
}
