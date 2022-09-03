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

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

class IterativeSolver<Node, Fact> extends Solver<Node, Fact> {

    public IterativeSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        while (true) {
            boolean flag = false;
            // 使用队列来倒序遍历CFG 使用set记录已经插入过队列的Node以避免重复插入
            Set<Node> isVisited = new HashSet<>();
            Queue<Node> queue = new LinkedList<>();
            queue.add(cfg.getExit());
            isVisited.add(cfg.getExit());
            //System.out.println(queue.isEmpty());
            // 遍历CFG中的每个结点，应该按照倒序来遍历，
            while (!queue.isEmpty()) {
                Node node = queue.peek();
                queue.remove();
                // 插入当前结点的前驱
                for (Node pred : cfg.getPredsOf(node)) {
                    if (!isVisited.contains(pred)) {
                        isVisited.add(pred);
                        queue.add(pred);
                    }
                }
                // 对于node结点的每个后继
                for (Node succ : cfg.getSuccsOf(node)) {
                    analysis.meetInto(result.getInFact(succ), result.getOutFact(node));
                }
                // 只要有一个true，说明至少一个节点的IN集合发生了改变，那么可以继续执行
                flag |= analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
            }
            if (!flag) break;
        }
    }
}
