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

import fj.P;
import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;

import java.util.*;
import java.util.concurrent.locks.Condition;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        /*
         * 死代码的几种情况
         * 控制流不可达代码：遍历cfg，把对所有可达的代码进行标记，剩下的就是不可达代码
         * 分支不可达代码：对于if语句判断条件值，如果是常量，必然会产生不可达代码，然后根据条件值来判断不可达代码是if还是then
         * 对于switch语句，如果条件值是常数，那么case语句可能是不可达的，这里有一个特殊情况：因为上一case如果不break或return则会继续执行，所以需要进行额外的判断
         * 对于分支不可达代码需要先进行常量传播分析条件是否为常量
         * 常量传播和活跃变量是自动完成的？
         * 无用赋值:进行活跃变量分析,如果左侧的变量是not live的，那么就是死代码，例外情况：右侧是一个函数调用，这个函数调用可能有副作用，将在interprocedural中被解决。
         */
        // 应该进行层次遍历，写个队列？
        // 对于Loops存在的问题是，在控制流图上不可达的结点被加进来了
        // 问题在于遍历cfg的时候是按照出边的target进行遍历，而不是按照跳转的目标进行加入的，应该调整加入的方式
        // 如果发现一条指令不能跳转，那么对于从这条指令后续的所有的指令也不能跳转，应该只加入确定能跳转的指令的后续到队列中。67
        Queue<Stmt> que = new LinkedList();
        que.offer(cfg.getEntry());
        Set<Stmt> isReached = new HashSet<>();
        while (!que.isEmpty()) {
            var stmt = que.remove();
            isReached.add(stmt);
            // 如果不是死代码，则加入
            //boolean isValid = true;
            for (var edge : cfg.getOutEdgesOf(stmt)) {
                if (isReached.contains(edge.getTarget()) || deadCode.contains(stmt))
                    continue;
                que.offer(edge.getTarget());
            }
            // 无用赋值检测
            var lvalue = stmt.getDef();
            if (lvalue.isPresent() && lvalue.get() instanceof Var) {
                DefinitionStmt<?, ?> definitionStmt = (DefinitionStmt<?, ?>) stmt;
                if (hasNoSideEffect(definitionStmt.getRValue()) && !liveVars.getOutFact(stmt).contains((Var) lvalue.get())) {
                    deadCode.add(stmt);
                }
            }
            // if找的应该是if和then语句的公共后继，在此之前的都是deadcode.
            // 从if和else分别找后继，凡是不是公共的都是deadcode。
            if (stmt instanceof If) {
                ConditionExp condition = ((If) stmt).getCondition();
                // 如何判断是不是常量？
                Value condValue = ConstantPropagation.evaluate(condition, constants.getInFact(stmt));
                if (condValue.isConstant()) {
                    // 对于if来说，出边一条是通往then，一条是通往else
                    // if和else的后继不可能只有一条语句，所以应该找出他们的公共部分
                    // 分别是if.Target和outEdge，这两个是否一样？肯定不一样，现在想不到，等会再写
                    if (condValue.getConstant() == 0) {
                        // then语句为死代码
                        deadCode.add(((If) stmt).getTarget());
                    } else {
                        // else语句为死代码，遍历stmt的出边，只要不是stmt的target，那么就是else语句
                        for (var edge : cfg.getOutEdgesOf(stmt)) {
                            if (!edge.getTarget().equals(((If) stmt).getTarget())) {
                                deadCode.add(edge.getTarget());
                            }
                        }
                    }
                }
            } else if (stmt instanceof SwitchStmt) {
                boolean caseflag = false;
                Set<Stmt> isVisited = new HashSet<>();
                if (ConstantPropagation.evaluate(((SwitchStmt) stmt).getVar(), constants.getInFact(stmt)).isConstant()) {
                    var switchValue = ConstantPropagation.evaluate(((SwitchStmt) stmt).getVar(), constants.getInFact(stmt)).getConstant();
                    int caseCounter = -1;
                    for (var casePair : ((SwitchStmt) stmt).getCaseTargets()) {
                        caseCounter++;
                        if (switchValue == casePair.first()) {
                            caseflag = true;
                            // 当前case的target
                            // gettarget和getoutedges的区别？我感觉一样
                            var curCase = casePair.second();
                            isVisited.add(curCase);
                            // 我应该记录下每个case跳转的目标，如果case在isVisited中，那么case就没有问题，否则就应该加入deadcode。
                            System.out.println(curCase.getIndex());
                            System.out.println(((SwitchStmt) stmt).getTarget(caseCounter));
                            isVisited.add(((SwitchStmt) stmt).getTarget(caseCounter));
                        } else {
                            var curCase = casePair.second();
                            if (isVisited.contains(casePair.second()))
                                isVisited.add(((SwitchStmt) stmt).getTarget(curCase.getIndex()));
                        }
                    }
                    if (!caseflag) {
                        isVisited.add(((SwitchStmt) stmt).getDefaultTarget());
                    }
                    for (var edge : cfg.getOutEdgesOf(stmt)) {
                        if (!isVisited.contains(edge.getTarget())) {
                            deadCode.add(edge.getTarget());
                        }
                    }
                }
            }
        }
        for (var stmt : cfg) {
            if (cfg.isEntry(stmt) || cfg.isExit(stmt))
                continue;
            if (!isReached.contains(stmt)) {
                deadCode.add(stmt);
            }
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
