//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.IO;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Diagnostics;
using System.Reflection;
using System.Linq;
using Microsoft.Boogie;
using System.Threading.Tasks;

namespace Microsoft.Dafny {

  public class HoleEvalGraph<T> {
    public HoleEvalGraph() { }
    public HoleEvalGraph(IEnumerable<T> vertices, IEnumerable<Tuple<T, T>> edges) {
      foreach (var vertex in vertices)
        AddVertex(vertex);

      foreach (var edge in edges)
        AddEdge(edge);
    }

    public Dictionary<T, HashSet<T>> AdjacencyList { get; } = new Dictionary<T, HashSet<T>>();

    public void AddVertex(T vertex) {
      AdjacencyList[vertex] = new HashSet<T>();
    }

    public void AddEdge(Tuple<T, T> edge) {
      if (AdjacencyList.ContainsKey(edge.Item1) && AdjacencyList.ContainsKey(edge.Item2)) {
        AdjacencyList[edge.Item1].Add(edge.Item2);
        AdjacencyList[edge.Item2].Add(edge.Item1);
      }
    }

    public HashSet<T> DFS(T start) {
      var visited = new HashSet<T>();

      if (!AdjacencyList.ContainsKey(start))
        return visited;

      var stack = new Stack<T>();
      stack.Push(start);

      while (stack.Count > 0) {
        var vertex = stack.Pop();

        if (visited.Contains(vertex))
          continue;

        visited.Add(vertex);

        foreach (var neighbor in AdjacencyList[vertex])
          if (!visited.Contains(neighbor))
            stack.Push(neighbor);
      }

      return visited;
    }

  }

  public class DirectedCallGraph<U, V> {
    public Dictionary<U, HashSet<Tuple<U, V>>> AdjacencyWeightList { get; } = new Dictionary<U, HashSet<Tuple<U, V>>>();

    public DirectedCallGraph() { }

    public void AddVertex(U vertex) {
      if (!AdjacencyWeightList.ContainsKey(vertex)) {
        AdjacencyWeightList[vertex] = new HashSet<Tuple<U, V>>();
      }
    }

    public void AddEdge(U source, U destination, V weight) {
      if (AdjacencyWeightList.ContainsKey(source) && AdjacencyWeightList.ContainsKey(destination)) {
        AdjacencyWeightList[source].Add(new Tuple<U, V>(destination, weight));
      }
    }
  }
}