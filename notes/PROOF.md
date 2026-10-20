# An optimal XOR coloring in Jensen--Toft 9.13

Let \(K(n,k,t)\) have the \(k\)-subsets of an \(n\)-element set as vertices,
with distinct \(S,U\) adjacent when \(|S\cap U|<t\). Let \(J(n,k)\) be the
Johnson graph, whose edges join \(k\)-sets intersecting in \(k-1\) elements.

**Theorem.** For every integer \(r\geq 1\), put \(k=2^r\). Then

\[
  \chi(K(2k,k,k-1))=\theta(J(2k,k))
    =\frac{1}{k+1}\binom{2k}{k}=C_k.
\]

Here \(\theta\) is the minimum number of vertex cliques covering a graph,
and \(C_k\) is the \(k\)-th Catalan number. The restriction \(r\geq1\)
ensures \(t=k-1>0\), as required in the original problem.

**Proof.** Let \(V=\mathbb F_2^{r+1}\), so \(|V|=2k\). For each \(S\subseteq V\),
write \(\sigma(S)=\bigoplus_{x\in S}x\). For a \(k\)-element set \(S\), define

\[
   c(S)=S\mathbin{\triangle}\{\sigma(S)\}.
\]

This toggles the unique ground element labeled by \(\sigma(S)\). Hence
\(|c(S)|\in\{k-1,k+1\}\), and in characteristic two
\(\sigma(c(S))=\sigma(S)\oplus\sigma(S)=0\).

Consider any zero-syndrome set \(T\) of size \(k-1\) or \(k+1\). If
\(|S|=k\) and \(|S\triangle T|=1\), let \(x\) be the element in that
symmetric difference. Then \(\sigma(S)=\sigma(T)\oplus x=x\), so
\(c(S)=T\). Conversely \(c(S)=T\) clearly implies
\(|S\triangle T|=1\). Thus the entire fiber of the color \(T\) is

\[
 \mathcal F_T=\{S\subseteq V: |S|=k,\ |S\triangle T|=1\}.
\]

If \(|T|=k-1\), this fiber consists of all \(k\)-sets containing \(T\),
and has \(2k-(k-1)=k+1\) members. If \(|T|=k+1\), it consists of all
\(k\)-subsets of \(T\), and again has \(k+1\) members. Two distinct
members of either fiber intersect in exactly \(k-1\) elements; in
particular, they are nonadjacent in \(K(2k,k,k-1)\). The nonempty fibers
partition its \(\binom{2k}{k}\) vertices, so \(c\) is a coloring with
\(\binom{2k}{k}/(k+1)\) colors.

For the lower bound, let \(\mathcal A\) be an independent family. Any two
distinct members of \(\mathcal A\) intersect in exactly \(k-1\) elements.
When \(|\mathcal A|\leq1\), its size is already at most \(k+1\).
Otherwise choose \(A=R\cup\{a\}\) and \(B=R\cup\{b\}\) in the family,
where \(|R|=k-1\) and \(a\ne b\) lie outside \(R\). Every other member
\(D\) either contains \(R\), or, to meet both \(A\) and \(B\) in at least
\(k-1\) elements, is
\(D=(R\setminus\{z\})\cup\{a,b\}\) for some \(z\in R\).
If no member of the latter kind occurs, the family is contained in the
star above \(R\), of size \(k+1\). If such a member occurs, any member
\(R\cup\{d\}\) of the former kind has \(d\in\{a,b\}\): otherwise its
intersection with \(D\) has only \(k-2\) elements. Now every member of
\(\mathcal A\) is a \(k\)-subset of the \((k+1)\)-set \(R\cup\{a,b\}\),
so again \(|\mathcal A|\leq k+1\). Every color class has size at most
\(k+1\), proving \(\chi\geq\binom{2k}{k}/(k+1)\).

Finally, \(K(2k,k,k-1)\) is the complement of \(J(2k,k)\). A coloring of
one is precisely a partition into vertex cliques of the other, and
allowing overlapping cliques cannot reduce the required number. This gives
the equality with \(\theta\). \(\square\)

**Structure of the centers.** The zero-syndrome \((k-1)\)-sets number
\(C_k/2\). Indeed, translation of every label of such an odd-sized set
by \(a\in V\) changes its syndrome by \(a\), so all \(2k\) syndrome
values occur equally often. The number is therefore
\(\binom{2k}{k-1}/(2k)=C_k/2\). Complementation takes these centers to
zero-syndrome \((k+1)\)-sets because the XOR of all labels in \(V\) is
zero. This gives \(C_k/2\) star fibers and \(C_k/2\) top fibers.

**Scope.** The theorem covers only
\((n,k,t)=(2^{r+1},2^r,2^r-1)\), \(r\geq1\), within the original
question, which asks for all \(n>k>t>0\). It does not establish
Jørgensen's more specific conjecture about the output of a greedy
lexicographic code algorithm. The published cases \(k=8,16\) are known;
the first case beyond those is \(k=32\).

References: T. R. Jensen and B. Toft, *Graph Coloring Problems*, Wiley,
1995, Problem 9.13, pp. 161--162; S. F. Jørgensen, "On the clique
covering numbers of Johnson graphs," *Designs, Codes and Cryptography*
**93** (2025), 3689--3705, DOI: 10.1007/s10623-025-01663-3.
