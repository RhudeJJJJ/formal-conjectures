/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons28
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1423 : Family 9 := level9.get ⟨163,by decide⟩
def sourceMap1423 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (sourceLabel 9 0 0 v)
def fusedMap1423 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1423_checked : acceptsGraphIso
    (source (graph core1423) (root 9) 0 0) DegreeOneSmallSpectrum720.graph sourceMap1423=true := by decide +kernel
theorem fusedMap1423_checked : acceptsGraphIso
    (fused (graph core1423) (root 9) 0 0) DegreeOneSmallSpectrum439.graph fusedMap1423=true := by decide +kernel
theorem certified1423 : Certified (graph core1423) (root 9) 0 0 :=
  of_native_maps core1423 DegreeOneSmallSpectrum720.graph DegreeOneSmallSpectrum439.graph
    sourceMap1423 fusedMap1423 sourceMap1423_checked fusedMap1423_checked
    DegreeOneSmallComparisons.comparison1423
#print axioms sourceMap1423_checked
#print axioms fusedMap1423_checked
#print axioms certified1423
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
