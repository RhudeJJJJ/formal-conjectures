/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons31
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1567 : Family 9 := level9.get ⟨296,by decide⟩
def sourceMap1567 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,9,10,11,5,6,7,8,3,4] (sourceLabel 9 0 0 v)
def fusedMap1567 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,8,9,10,11,4,5,6,7,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1567_checked : acceptsGraphIso
    (source (graph core1567) (root 9) 0 0) SmallGeFourSpectrum144.graph sourceMap1567=true := by decide +kernel
theorem fusedMap1567_checked : acceptsGraphIso
    (fused (graph core1567) (root 9) 0 0) SmallGeFourSpectrum107.graph fusedMap1567=true := by decide +kernel
theorem certified1567 : Certified (graph core1567) (root 9) 0 0 :=
  of_native_maps core1567 SmallGeFourSpectrum144.graph SmallGeFourSpectrum107.graph
    sourceMap1567 fusedMap1567 sourceMap1567_checked fusedMap1567_checked
    DegreeOneSmallComparisons.comparison1567
#print axioms sourceMap1567_checked
#print axioms fusedMap1567_checked
#print axioms certified1567
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
