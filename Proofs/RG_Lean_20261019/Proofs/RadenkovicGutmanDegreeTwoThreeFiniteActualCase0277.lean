/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0277 : Family 9 := level9.get ⟨380,by decide⟩
def sourceMap0277 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (sourceLabel 9 0 0 v)
def fusedMap0277 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,11,7,8,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0277_checked : acceptsGraphIso
    (source (graph core0277) (root 9) 0 0) DegreeOneSmallSpectrum738.graph sourceMap0277=true := by decide +kernel
theorem fusedMap0277_checked : acceptsGraphIso
    (fused (graph core0277) (root 9) 0 0) DegreeOneSmallSpectrum735.graph fusedMap0277=true := by decide +kernel
theorem certified0277 : Certified (graph core0277) (root 9) 0 0 :=
  of_native_maps core0277 DegreeOneSmallSpectrum738.graph DegreeOneSmallSpectrum735.graph
    sourceMap0277 fusedMap0277 sourceMap0277_checked fusedMap0277_checked
    DegreeTwoThreeFiniteComparisons.comparison0277
#print axioms sourceMap0277_checked
#print axioms fusedMap0277_checked
#print axioms certified0277
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
