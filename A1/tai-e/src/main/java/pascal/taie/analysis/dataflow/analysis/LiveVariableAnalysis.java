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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

import java.util.List;
import java.util.Optional;

/**
 * Implementation of classic live variable analysis.
 */
// 这个LiveVariableAnalysis是AbstractDataflowAnalysis的派生类，同时也继承了父类中定义的函数接口和数据成员
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        // IN[exit] = 空集
        // getExit返回的实际上是cfg的一个node，这个node的类型是Stmt，
        // IN
        return new SetFact<>();
    }
// 初始化阶段应该将IN和OUT同样初始化为空集，那么如何初始化呢？
    @Override
    public SetFact<Var> newInitialFact() {
        // TODO - finish me
        // for each block B, IN[B] = 空集
        // 对每个block都需要有一个
        return new SetFact<>();
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        // TODO - finish me
        // meetInto: OUT[s2] = IN[S2]  IN[S2] = meetInto(IN[S2], OUT[S1])
        // meetInto的作用是把fact集合合并到target集合， fact是IN[S2]，target是OUT[S1]
        // OUTB的计算方法是对所有的后续的IN求并集
        // 对于每个后继，都需要将后继的IN与target meetInto后再求并，也就是说对target和fact求并集
        target.union(fact);
    }

    @Override
    // 需要判断前后IN是否发生了变化
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        // TODO - finish me
        // IN = use U (OUT - def)
        Optional<LValue> def = stmt.getDef();
        def.ifPresent(lValue -> out.remove((Var) lValue));
        List<RValue> uses = stmt.getUses();
        for (RValue use : uses) {
            out.add((Var) use);
        }
        // 如果in发生了变化，那么应该返回true，否则返回false
        if (in.equals(out)) {
            in = out;
            return false;
        } else {
            in = out;
            return true;
        }
    }
}
