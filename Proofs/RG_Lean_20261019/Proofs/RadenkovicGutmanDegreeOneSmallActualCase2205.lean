/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2205 : Family 10 := level10.get ⟨725,by decide⟩
def sourceMap2205 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2205 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2205_checked : acceptsGraphIso
    (source (graph core2205) (root 10) 0 0) DegreeOneSmallSpectrum1861.graph sourceMap2205=true := by decide +kernel
theorem fusedMap2205_checked : acceptsGraphIso
    (fused (graph core2205) (root 10) 0 0) DegreeOneSmallSpectrum1349.graph fusedMap2205=true := by decide +kernel
theorem certified2205 : Certified (graph core2205) (root 10) 0 0 :=
  of_native_maps core2205 DegreeOneSmallSpectrum1861.graph DegreeOneSmallSpectrum1349.graph
    sourceMap2205 fusedMap2205 sourceMap2205_checked fusedMap2205_checked
    DegreeOneSmallComparisons.comparison2205
#print axioms sourceMap2205_checked
#print axioms fusedMap2205_checked
#print axioms certified2205
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
