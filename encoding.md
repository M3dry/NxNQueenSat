## Encoding
### Variables
- $w_{x,y}$ ... white queen at $(x,y)$
- $b_{x,y}$ ... black queen at $(x,y)$
- $s_{x,y,c,k}$ ... the number of queens of color $c$ at, and before, $(x,y)$ is at least $k$. Meaning all rows of the board above $(x,y)$ and all the tiles to the left of $(x,y)$, and including $(x,y)$.

### No two queens share the same spot
For any tile $(x,y)$ let $w = w_{x,y}$, and $b = b_{x,y}$, then $w \implies \neg b$ and $b \implies \neg w$ encodes the condition. In CNF this is $\neg w \lor \neg b$.

### The number of queens is exactly $k$
The final encoding for each color $c$ is simply $s_{n - 1, n - 1,c,k} \land \neg s_{n - 1, n - 1,c,k + 1}$, i.e. the last tile's number of queens is $k$, but also isn't $k + 1$.
Encoding the sum variables $s_{x,y,c,k}$ is harder, for that we encode:

#### Initial case:
For all $c$ $s_{0,0,c,0}$ is always true, and $c_{0,0} \iff s_{0,0,c,1}$ must be true. But also for any $k > 1$ $s_{0,0,c,k}$ is false. Thus in CNF we get: $s_{0,0,c,0} \land (\neg c_{0,0} \lor s_{0,0,c,1}) \land (c_{0,0} \lor \neg s_{0,0,c,1}) \land \bigwedge_{i > 1}^{k + 1} \neg s_{0,0,c,i}$

#### Case for each $(x,y) \neq (0,0)$:
Let $(prev_x,prev_y)$ be the previous coordinate, i.e.
$$
(prev_x,prev_y) =
\begin{cases}
    (x - 1, y) & \text{if } x > 0 \\
    (n - 1, y - 1) & \text{if } x = 0 \land y > 0
\end{cases}
$$

Then we need to encode these rules for every color $c$:

1. for all $0 \le z \le k + 1$ $s_{prev_x,prev_y,c,z} \implies s_{x,y,c,z}$
2. for all $1 \le z \le k + 1$ $c_{x,y} \land s_{prev_x,prev_y,c,z - 1} \implies s_{x,y,c,z}$
3. for all $1 \le z \le k + 1$ $s_{x,y,c,z} \implies s_{prev_x,prev_y,c,z} \lor (s_{prev_x,prev_y,c,z - 1} \land c_{x,y})$

In CNF they're encoded like so (omitting the quantifiers as they're the same as above):

1. $s_{x,y,z,c} \lor \neg s_{prev_x,prev_y,z,c}$
2. $s_{x,y,z,c} \lor \neg s_{prev_x,prev_y,z - 1,c} \lor \neg c_{x,y}$
3. $(\neg s_{x,y,z,c} \lor s_{prev_x,prev_y,z,c} \lor s_{prev_x,prev_y,z - 1,c}) \land (\neg s_{x,y,z,c} \lor s_{prev_x,prev_y,z,c} \lor c_{x,y})$

### No queen attacks any queen of the opposite color
For every $(x,y)$, color $c$, and let $c'$ be the opposite color, we encode:

1. $c_{x,y} -> \neg c'_{x',y}$ for all $x' \neq x$ ... row attack condition
2. $c_{x,y} -> \neg c'_{x,y'}$ for all $y' \neq y$ ... column attack condition
2. $c_{x,y} -> \neg c'_{x',y'}$ for all $x',y' \neq x,y$ that are on one of the diagonals originating from $(x,y)$ ... diagonal attack condition

This can be easily turned into CNF since it's just a conjunction of implications between variables.
