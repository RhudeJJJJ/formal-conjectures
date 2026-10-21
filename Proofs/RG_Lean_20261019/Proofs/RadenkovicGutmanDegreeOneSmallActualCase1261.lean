/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons25
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1261 : Family 9 := level9.get ⟨39,by decide⟩
def sourceMap1261 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![3,2,1,0,8,9,10,11,6,7,4,5] (sourceLabel 9 0 0 v)
def fusedMap1261 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (fusedLabel 9 0 0 v)
theorem sourceMap1261_checked : acceptsGraphIso
    (source (graph core1261) (root 9) 0 0) DegreeOneSmallSpectrum440.graph sourceMap1261=true := by decide +kernel
theorem fusedMap1261_checked : acceptsGraphIso
    (fused (graph core1261) (root 9) 0 0) DegreeOneSmallSpectrum388.graph fusedMap1261=true := by decide +kernel
theorem certified1261 : Certified (graph core1261) (root 9) 0 0 :=
  of_native_maps core1261 DegreeOneSmallSpectrum440.graph DegreeOneSmallSpectrum388.graph
    sourceMap1261 fusedMap1261 sourceMap1261_checked fusedMap1261_checked
    DegreeOneSmallComparisons.comparison1261
#print axioms sourceMap1261_checked
#print axioms fusedMap1261_checked
#print axioms certified1261
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
