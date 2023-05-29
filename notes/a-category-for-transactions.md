I found that securities and transactions form the following category, for which I do not know a precise name. I call it a "category for transactions" for now.

```mermaid

```latex
\documentclass{article}
\usepackage{amsmath}
\usepackage{tikz-cd}

\begin{document}
\begin{center}
\begin{tikzcd}[sep=2cm, cells={nodes={minimum width=2cm,minimum height=1cm,align=center,font=\itshape}}]
    1 \arrow[r, "Initial", font=\scriptsize, bend left=20] & \text{\textbf{Alive}} \arrow[loop right, distance=3cm, "NonTerminal", font=\scriptsize] \arrow[d, "Terminal", font=\scriptsize, bend left=20] \\
    & \text{\textbf{Dead}}
\end{tikzcd}
\end{center}
\end{document}
```