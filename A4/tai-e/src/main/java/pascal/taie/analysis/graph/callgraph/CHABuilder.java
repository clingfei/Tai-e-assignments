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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import pascal.taie.language.type.Type;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod method = workList.remove();
            if (!callGraph.addReachableMethod(method))
                continue;
            for (var callSite : callGraph.getCallSitesIn(method)) {
                Set<JMethod> T = resolve(callSite);
                for (JMethod jMethod : T) {
                    if (jMethod == null) continue;
                    Edge<Invoke, JMethod> edge = new Edge<>(CallGraphs.getCallKind(callSite), callSite, jMethod);
                    callGraph.addEdge(edge);
                    workList.add(jMethod);
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T = new HashSet<>();
        MethodRef method = callSite.getMethodRef();
        // callsite的函数签名，应该用哪个函数？
        // subSignature和signature的区别在于，signature有类，而subSignature没有类。
        JClass jClass = method.getDeclaringClass();
        Subsignature jSubsignature = method.getSubsignature();
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC -> T.add(jClass.getDeclaredMethod(jSubsignature));
            case SPECIAL -> T.add(dispatch(jClass, jSubsignature));
            case VIRTUAL, INTERFACE -> {
                Set<JClass> allSubJClasses = getAllSubClasses(jClass);
                for (JClass jClassIter : allSubJClasses) {
                    T.add(dispatch(jClassIter, jSubsignature));
                }
            }
        }
        return T;
    }

    private Set<JClass> getAllSubClasses(JClass jClass) {
        Set<JClass> subClasses = new HashSet<>(), jNewClasses = new HashSet<>();
        subClasses.addAll(hierarchy.getDirectSubclassesOf(jClass));
        subClasses.addAll(hierarchy.getDirectImplementorsOf(jClass));
        subClasses.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
        for (JClass jClassIter : subClasses) {
            jNewClasses.addAll(getAllSubClasses(jClassIter));
        }
        subClasses.addAll(jNewClasses);
        subClasses.add(jClass);
        return subClasses;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod method = jclass.getDeclaredMethod(subsignature);
        // what's the meaning for isNative?
        // return Dispatch(c', m), c' is the superclass of jclass
        if (method == null || method.isAbstract()) {
            JClass superClass = jclass.getSuperClass();
            if (superClass == null) return null;
            else return dispatch(superClass, subsignature);
        } else {
            return method;
        }
    }
}
