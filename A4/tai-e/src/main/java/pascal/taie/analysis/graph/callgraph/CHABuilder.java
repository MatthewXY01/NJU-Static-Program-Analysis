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
        callGraph.addReachableMethod(entry);
        Deque<JMethod> workList = new LinkedList<>();
        workList.addLast(entry);
        while (!workList.isEmpty()) {
            JMethod jmethod = workList.removeFirst();
            callGraph.callSitesIn(jmethod).forEach( callSite -> {
                // cs in method -> get resolved targets via CHA -> ad edge(cs->m) -> add m to workList
                CallKind callKind = CallGraphs.getCallKind(callSite);
                resolve(callSite).forEach( resolvedMethod -> {
                    callGraph.addEdge(new Edge<>(callKind, callSite, resolvedMethod));
                    if (callGraph.addReachableMethod(resolvedMethod)) workList.add(resolvedMethod);
                });
            });
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> resolvedMethodSet = new HashSet<>();
        JMethod resolvedMethod;
        MethodRef methodRef = callSite.getMethodRef();
        JClass declaredClass = methodRef.getDeclaringClass();
        Subsignature subsig = methodRef.getSubsignature();
        if (callSite.isStatic() || callSite.isSpecial()) {
            resolvedMethod = dispatch(declaredClass, subsig);
            if (resolvedMethod != null && !resolvedMethod.isAbstract()) resolvedMethodSet.add(resolvedMethod);
        }else if (callSite.isVirtual() || callSite.isInterface()) {
            Set<JClass> visitedClasses = new HashSet<>();
            Deque<JClass> classStack = new LinkedList<>();
            if (callSite.isInterface()) {
                // invokeinterface
                Set<JClass> visitedInterfaces = new HashSet<>();
                Deque<JClass> ifaceStack = new LinkedList<>();
                visitedInterfaces.add(declaredClass);
                ifaceStack.push(declaredClass);
                while (!ifaceStack.isEmpty()) {
                    JClass iface = ifaceStack.pop();
                    hierarchy.getDirectSubinterfacesOf(iface)
                            .forEach( subIface -> {if (visitedInterfaces.add(subIface)) ifaceStack.push(subIface);});
                    hierarchy.getDirectImplementorsOf(iface)
                            .forEach( impl -> {if (visitedClasses.add(impl)) classStack.push(impl);});
                }
            } else {
                // invokevirtual
                classStack.push(declaredClass);
            }
            while (!classStack.isEmpty()) {
                JClass jclass = classStack.pop();
                // could hava redundant dispatch, maybe do visitedPair<JClass, Subsignature> check?
                resolvedMethod = dispatch(jclass, subsig);
                if (resolvedMethod != null && !resolvedMethod.isAbstract()) resolvedMethodSet.add(resolvedMethod);
                for (JClass subClass: hierarchy.getDirectSubclassesOf(jclass)) {
                    if (visitedClasses.add(subClass)) classStack.push(subClass);
                }
            }
        }
        return resolvedMethodSet;
//        return null;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod targetMethod = jclass.getDeclaredMethod(subsignature);
        if (targetMethod != null) {
            return targetMethod;
        }
        JClass superClass = jclass.getSuperClass();
        if (superClass != null) return dispatch(superClass, subsignature);
        return null;
    }
}
