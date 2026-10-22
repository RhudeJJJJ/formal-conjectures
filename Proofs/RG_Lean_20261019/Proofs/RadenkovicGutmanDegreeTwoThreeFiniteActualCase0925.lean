/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0925 : Family 10 := level10.get ⟨1512,by decide⟩
def sourceMap0925 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,10,11,12,2,3,4,5,6,7,8,9] (sourceLabel 10 0 0 v)
def fusedMap0925 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,10,11,12,2,3,4,5,6,7,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0925_checked : acceptsGraphIso
    (source (graph core0925) (root 10) 0 0) DegreeOneSmallSpectrum1540.graph sourceMap0925=true := by decide +kernel
theorem fusedMap0925_checked : acceptsGraphIso
    (fused (graph core0925) (root 10) 0 0) DegreeOneSmallSpectrum1536.graph fusedMap0925=true := by decide +kernel
theorem certified0925 : Certified (graph core0925) (root 10) 0 0 :=
  of_native_maps core0925 DegreeOneSmallSpectrum1540.graph DegreeOneSmallSpectrum1536.graph
    sourceMap0925 fusedMap0925 sourceMap0925_checked fusedMap0925_checked
    DegreeTwoThreeFiniteComparisons.comparison0925
#print axioms sourceMap0925_checked
#print axioms fusedMap0925_checked
#print axioms certified0925
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
