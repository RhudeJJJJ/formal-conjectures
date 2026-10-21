/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1253 : Family 9 := level9.get ⟨34,by decide⟩
def sourceMap1253 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,8,9,10,11,6,7,4,5] (sourceLabel 9 0 0 v)
def fusedMap1253 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1253_checked : acceptsGraphIso
    (source (graph core1253) (root 9) 0 0) DegreeOneSmallSpectrum464.graph sourceMap1253=true := by decide +kernel
theorem fusedMap1253_checked : acceptsGraphIso
    (fused (graph core1253) (root 9) 0 0) DegreeOneSmallSpectrum393.graph fusedMap1253=true := by decide +kernel
theorem certified1253 : Certified (graph core1253) (root 9) 0 0 :=
  of_native_maps core1253 DegreeOneSmallSpectrum464.graph DegreeOneSmallSpectrum393.graph
    sourceMap1253 fusedMap1253 sourceMap1253_checked fusedMap1253_checked
    DegreeOneSmallComparisons.comparison1253
#print axioms sourceMap1253_checked
#print axioms fusedMap1253_checked
#print axioms certified1253
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
