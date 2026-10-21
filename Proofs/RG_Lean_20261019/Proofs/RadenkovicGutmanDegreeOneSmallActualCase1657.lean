/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons33
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1657 : Family 9 := level9.get ⟨416,by decide⟩
def sourceMap1657 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,4,2,3] (sourceLabel 9 0 0 v)
def fusedMap1657 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1657_checked : acceptsGraphIso
    (source (graph core1657) (root 9) 0 0) DegreeOneSmallSpectrum732.graph sourceMap1657=true := by decide +kernel
theorem fusedMap1657_checked : acceptsGraphIso
    (fused (graph core1657) (root 9) 0 0) DegreeOneSmallSpectrum777.graph fusedMap1657=true := by decide +kernel
theorem certified1657 : Certified (graph core1657) (root 9) 0 0 :=
  of_native_maps core1657 DegreeOneSmallSpectrum732.graph DegreeOneSmallSpectrum777.graph
    sourceMap1657 fusedMap1657 sourceMap1657_checked fusedMap1657_checked
    DegreeOneSmallComparisons.comparison1657
#print axioms sourceMap1657_checked
#print axioms fusedMap1657_checked
#print axioms certified1657
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
