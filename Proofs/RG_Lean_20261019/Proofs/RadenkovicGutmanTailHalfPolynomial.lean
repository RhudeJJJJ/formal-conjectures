/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanTailIntegral

/-! Polynomial forms from the original finite Weyl-disk half-plane test.
Here h=1/d,u=1/y,a=y(P-y),b=y(Q-y). Complex coefficients are multiplied by
u^2; the imaginary parts have one further factor u. -/
namespace Gebendorfer.RadenkovicGutman.TailHalfPolynomial
noncomputable section
def ar (u a b : ℝ) := 1+(a+b-1)*u^2+a*b*u^4
def ai (u a b : ℝ) := -2-(a+b)*u^2
def nr (u a b : ℝ) := -2+(4-a-b)*u^2
def ni (u a b : ℝ) := 6+2*(a+b)*u^2
def br (u a b : ℝ) := 1+(a+b+1)*u^2+a*b*u^4
def bi (u a b : ℝ) := -1-(a+b)*u^2
def dr (u a b : ℝ) := -1-(a+b)*u^2
def di (u a b : ℝ) := 2+2*(a+b)*u^2
def aa (u a b : ℝ) := (ar u a b)^2+u^2*(ai u a b)^2
def bb (u a b : ℝ) := (br u a b)^2+u^2*(bi u a b)^2
def xForm (u a b : ℝ) := 2*(bb u a b*(ar u a b*nr u a b+u^2*ai u a b*ni u a b)-aa u a b*(br u a b*dr u a b+u^2*bi u a b*di u a b))
def tForm (u a b : ℝ) := -2*(bb u a b*(ai u a b*nr u a b-ar u a b*ni u a b)-aa u a b*(bi u a b*dr u a b-br u a b*di u a b))
def cForm (u a b : ℝ) := bb u a b*((nr u a b)^2+u^2*(ni u a b)^2)-aa u a b*((dr u a b)^2+u^2*(di u a b)^2)
def vForm (h u a b : ℝ) := xForm u a b*(2*h-1)+tForm u a b*(h+u^2/2)+h*cForm u a b
def kForm (h u a b : ℝ) := (vForm h u a b)^2-u^2/4*((xForm u a b)^2+u^2*(tForm u a b)^2)
end
end Gebendorfer.RadenkovicGutman.TailHalfPolynomial
