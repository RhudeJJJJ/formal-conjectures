/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons30
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1543 : Family 9 := level9.get ⟨271,by decide⟩
def sourceMap1543 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,7,8,9,10,11,5,6,3,4] (sourceLabel 9 0 0 v)
def fusedMap1543 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,6,7,8,9,10,11,4,5,2,3] (fusedLabel 9 0 0 v)
theorem sourceMap1543_checked : acceptsGraphIso
    (source (graph core1543) (root 9) 0 0) DegreeOneSmallSpectrum728.graph sourceMap1543=true := by decide +kernel
theorem fusedMap1543_checked : acceptsGraphIso
    (fused (graph core1543) (root 9) 0 0) DegreeOneSmallSpectrum579.graph fusedMap1543=true := by decide +kernel
theorem certified1543 : Certified (graph core1543) (root 9) 0 0 :=
  of_native_maps core1543 DegreeOneSmallSpectrum728.graph DegreeOneSmallSpectrum579.graph
    sourceMap1543 fusedMap1543 sourceMap1543_checked fusedMap1543_checked
    DegreeOneSmallComparisons.comparison1543
#print axioms sourceMap1543_checked
#print axioms fusedMap1543_checked
#print axioms certified1543
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
