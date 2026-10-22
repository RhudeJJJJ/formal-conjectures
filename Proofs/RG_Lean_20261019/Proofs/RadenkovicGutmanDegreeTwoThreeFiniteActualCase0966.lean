/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0966 : Family 10 := level10.get ⟨1619,by decide⟩
def sourceMap0966 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0966 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0966_checked : acceptsGraphIso
    (source (graph core0966) (root 10) 0 0) DegreeOneSmallSpectrum1709.graph sourceMap0966=true := by decide +kernel
theorem fusedMap0966_checked : acceptsGraphIso
    (fused (graph core0966) (root 10) 0 0) DegreeOneSmallSpectrum1708.graph fusedMap0966=true := by decide +kernel
theorem certified0966 : Certified (graph core0966) (root 10) 0 0 :=
  of_native_maps core0966 DegreeOneSmallSpectrum1709.graph DegreeOneSmallSpectrum1708.graph
    sourceMap0966 fusedMap0966 sourceMap0966_checked fusedMap0966_checked
    DegreeTwoThreeFiniteComparisons.comparison0966
#print axioms sourceMap0966_checked
#print axioms fusedMap0966_checked
#print axioms certified0966
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
