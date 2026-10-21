/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons29
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1463 : Family 9 := level9.get ⟨201,by decide⟩
def sourceMap1463 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,3,4] (sourceLabel 9 0 0 v)
def fusedMap1463 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1463_checked : acceptsGraphIso
    (source (graph core1463) (root 9) 0 0) DegreeOneSmallSpectrum753.graph sourceMap1463=true := by decide +kernel
theorem fusedMap1463_checked : acceptsGraphIso
    (fused (graph core1463) (root 9) 0 0) DegreeOneSmallSpectrum502.graph fusedMap1463=true := by decide +kernel
theorem certified1463 : Certified (graph core1463) (root 9) 0 0 :=
  of_native_maps core1463 DegreeOneSmallSpectrum753.graph DegreeOneSmallSpectrum502.graph
    sourceMap1463 fusedMap1463 sourceMap1463_checked fusedMap1463_checked
    DegreeOneSmallComparisons.comparison1463
#print axioms sourceMap1463_checked
#print axioms fusedMap1463_checked
#print axioms certified1463
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
