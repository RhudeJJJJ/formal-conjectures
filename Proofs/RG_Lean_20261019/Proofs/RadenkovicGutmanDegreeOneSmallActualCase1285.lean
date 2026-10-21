/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1285 : Family 9 := level9.get ⟨56,by decide⟩
def sourceMap1285 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,10,11] (sourceLabel 9 0 0 v)
def fusedMap1285 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1285_checked : acceptsGraphIso
    (source (graph core1285) (root 9) 0 0) DegreeOneSmallSpectrum466.graph sourceMap1285=true := by decide +kernel
theorem fusedMap1285_checked : acceptsGraphIso
    (fused (graph core1285) (root 9) 0 0) DegreeOneSmallSpectrum469.graph fusedMap1285=true := by decide +kernel
theorem certified1285 : Certified (graph core1285) (root 9) 0 0 :=
  of_native_maps core1285 DegreeOneSmallSpectrum466.graph DegreeOneSmallSpectrum469.graph
    sourceMap1285 fusedMap1285 sourceMap1285_checked fusedMap1285_checked
    DegreeOneSmallComparisons.comparison1285
#print axioms sourceMap1285_checked
#print axioms fusedMap1285_checked
#print axioms certified1285
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
