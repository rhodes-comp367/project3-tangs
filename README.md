[![Review Assignment Due Date](https://classroom.github.com/assets/deadline-readme-button-22041afd0340ce965d47ae6ef1cefeee28c7c493a6346c4f15d667ab976d596c.svg)](https://classroom.github.com/a/dPwN1w3S)
# Final project

**Explain the general theme and specific features of your project.**
The general theme is matrix operations. This involves defining a matrix in terms of
m vectors of n vectors. We defined matrix additions/subtractions and scalar multiplication, and 
then proved properties for addition and scalar multiplications for natural numbers (see Matrix-Nat.agda). We also defined matrix multiplication, which is nice in Agda since it affords us to be able to limit the parameters to only allow mult between mxr and rxn matrices, in other words, matrices with a shared dimension. To implement this, we had to be creative. Since case splitting vectors of vectors would expose only the rows, but we needed rows of A
and cols of B. We implemented matrix transpose to make the cols of B the rows. We then used the
vector dot product definition of the elements to build the final matrix. Lastly, we defined 
finding the determinant of a matrix. 

**Cite any resources or existing code you used.**
Section 1.3 ("Matrices and Matrix Operations") and Section 2.1 ("Determinants by Cofactor Expansions") in *Elementary Linear Algebra, 12th Edition* by Howard Anton and Anton Kaul

**Discuss any challenges, or anything you'd like feedback on.**
Finding the determinant of a matrix in terms of cofactor expansion was the main challenge
of our project. This involved breaking it down into different steps and helpers, which
we believe demonstrates a good understanding of both the topic and the recursive
nature of Agda. This one in particular took a majority of our work and time. If 
there are other ways it should have been implemented (for instance including the 2x2 in the 
cofactor/sum of products definition of a determinant), then let us know as we will appreciate any 
feedback. Thanks! 


