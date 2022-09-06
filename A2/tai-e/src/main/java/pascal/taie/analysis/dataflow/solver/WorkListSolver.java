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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.ir.stmt.DefinitionStmt;

import java.util.LinkedList;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        initializeForward(cfg, result);
        Queue<Node> workList = new LinkedList<>();
        workList.offer(cfg.getEntry());
        // 出错的原因归根结底在于在构建workList时，没有将(p, NAC)加入进去，
        // 在initialize 的时候没有将In设置为NAC？
//        for (var node:cfg) {
//            System.out.println(node.toString());
//        }
//        for (var node : cfg.getIR().getVars())
//            System.out.println(node.toString());
        for (var node : cfg) {
            workList.offer(node);
        }
        while (!workList.isEmpty()) {
            Node curNode = workList.remove();
            for (Node node : cfg.getPredsOf(curNode)) {
                analysis.meetInto(result.getOutFact(node), result.getInFact(curNode));
            }

            if (!analysis.transferNode(curNode, result.getInFact(curNode), result.getOutFact(curNode)))
                for (var node : cfg.getSuccsOf(curNode))
                    workList.offer(node);
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
