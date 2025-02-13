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
import pascal.taie.util.collection.Sets;

import java.util.Collections;
import java.util.Iterator;
import java.util.Set;
import java.util.stream.Collectors;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        Set<Node> newWorkList = Sets.newHybridSet(cfg.getNodes());
        Set<Node> oldWorkList = Sets.newHybridSet(Collections.emptySet());
        Set<Node> tmpWorkList;
        while (!newWorkList.isEmpty()) {
            tmpWorkList = oldWorkList;
            oldWorkList = newWorkList;
            newWorkList = tmpWorkList;
            boolean hasChanged;
            for (Node node : oldWorkList) {
                hasChanged = false;
                if (cfg.isEntry(node) || cfg.isExit(node)) continue;
                for (Node preNode : cfg.getPredsOf(node)) {
                    analysis.meetInto(result.getOutFact(preNode), result.getInFact(node));
                }
                hasChanged = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
                if (hasChanged) {
                    newWorkList.addAll(cfg.getSuccsOf(node));
                }
            }
            oldWorkList.clear();
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
