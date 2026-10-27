/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons80
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4014 : Family 2 := level2.get ⟨1,by decide⟩
def sourceMap4014 : (Vertices 2 ⊕ Fin 2 ⊕ Fin 8) → Fin 13 :=
  fun v => ![3,6,7,4,5,2,1,0,8,9,10,11,12] (sourceLabel 2 1 7 v)
def fusedMap4014 : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 1 7 v)
theorem sourceMap4014_checked : acceptsGraphIso
    (source (graph core4014) (root 2) 1 7) DegreeOneSmallSpectrum922.graph sourceMap4014=true := by decide +kernel
theorem fusedMap4014_checked : acceptsGraphIso
    (fused (graph core4014) (root 2) 1 7) DegreeOneSmallSpectrum856.graph fusedMap4014=true := by decide +kernel
theorem certified4014 : Certified (graph core4014) (root 2) 1 7 :=
  of_native_maps core4014 DegreeOneSmallSpectrum922.graph DegreeOneSmallSpectrum856.graph
    sourceMap4014 fusedMap4014 sourceMap4014_checked fusedMap4014_checked
    DegreeTwoThreeFiniteComparisons.comparison4014
#print axioms sourceMap4014_checked
#print axioms fusedMap4014_checked
#print axioms certified4014
def sourceMap4014swap : (Vertices 2 ⊕ Fin 8 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,6,7,2,1,0,8,9,10,11,12,4,5] (sourceLabel 2 7 1 v)
def fusedMap4014swap : (Vertices 2 ⊕ Fin 10) → Fin 13 :=
  fun v => ![4,5,6,3,2,1,0,7,8,9,10,11,12] (fusedLabel 2 7 1 v)
theorem sourceMap4014swap_checked : acceptsGraphIso
    (source (graph core4014) (root 2) 7 1) DegreeOneSmallSpectrum922.graph sourceMap4014swap=true := by decide +kernel
theorem fusedMap4014swap_checked : acceptsGraphIso
    (fused (graph core4014) (root 2) 7 1) DegreeOneSmallSpectrum856.graph fusedMap4014swap=true := by decide +kernel
theorem certified4014swap : Certified (graph core4014) (root 2) 7 1 :=
  of_native_maps core4014 DegreeOneSmallSpectrum922.graph DegreeOneSmallSpectrum856.graph
    sourceMap4014swap fusedMap4014swap sourceMap4014swap_checked fusedMap4014swap_checked
    DegreeTwoThreeFiniteComparisons.comparison4014
#print axioms sourceMap4014swap_checked
#print axioms fusedMap4014swap_checked
#print axioms certified4014swap
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
