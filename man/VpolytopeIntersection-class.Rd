% Generated by roxygen2: do not edit by hand
% Please edit documentation in R/VpolytopeIntersectionClass.R
\docType{class}
\name{VpolytopeIntersection-class}
\alias{VpolytopeIntersection-class}
\alias{VpolytopeIntersection}
\title{An R class to represent the intersection of two V-polytopes}
\description{
An intersection of two V-polytopes is defined by the intersection of the two coresponding convex hulls.
}
\details{
\describe{
   \item{V1}{An \eqn{m\times d} numerical matrix that contains the vertices of the first V-polytope (row-wise).}
   
   \item{V2}{An \eqn{q\times d} numerical matrix that contains the vertices of the second V-polytope (row-wise).}

   \item{volume}{The volume of the polytope if it is known, \eqn{NaN} otherwise by default.}
   
   \item{type}{A character with default value 'VpolytopeIntersection', to declare the representation of the polytope.}
}
}
\examples{
P1 = gen_simplex(2,'V')
P2 = gen_cross(2,'V')
P = VpolytopeIntersection(V1 = P1@V, V2 = P2@V)

}
