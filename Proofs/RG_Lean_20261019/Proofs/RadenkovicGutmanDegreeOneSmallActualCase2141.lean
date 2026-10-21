/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2141 : Family 10 := level10.get ⟨590,by decide⟩
def sourceMap2141 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2141 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2141_checked : acceptsGraphIso
    (source (graph core2141) (root 10) 0 0) DegreeOneSmallSpectrum1813.graph sourceMap2141=true := by decide +kernel
theorem fusedMap2141_checked : acceptsGraphIso
    (fused (graph core2141) (root 10) 0 0) DegreeOneSmallSpectrum1136.graph fusedMap2141=true := by decide +kernel
theorem certified2141 : Certified (graph core2141) (root 10) 0 0 :=
  of_native_maps core2141 DegreeOneSmallSpectrum1813.graph DegreeOneSmallSpectrum1136.graph
    sourceMap2141 fusedMap2141 sourceMap2141_checked fusedMap2141_checked
    DegreeOneSmallComparisons.comparison2141
#print axioms sourceMap2141_checked
#print axioms fusedMap2141_checked
#print axioms certified2141
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
