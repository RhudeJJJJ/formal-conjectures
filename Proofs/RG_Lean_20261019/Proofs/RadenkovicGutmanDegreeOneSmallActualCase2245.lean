/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2245 : Family 10 := level10.get ⟨801,by decide⟩
def sourceMap2245 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (sourceLabel 10 0 0 v)
def fusedMap2245 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,8,9,10,11,12,1,2,3,4,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2245_checked : acceptsGraphIso
    (source (graph core2245) (root 10) 0 0) DegreeOneSmallSpectrum1193.graph sourceMap2245=true := by decide +kernel
theorem fusedMap2245_checked : acceptsGraphIso
    (fused (graph core2245) (root 10) 0 0) DegreeOneSmallSpectrum1187.graph fusedMap2245=true := by decide +kernel
theorem certified2245 : Certified (graph core2245) (root 10) 0 0 :=
  of_native_maps core2245 DegreeOneSmallSpectrum1193.graph DegreeOneSmallSpectrum1187.graph
    sourceMap2245 fusedMap2245 sourceMap2245_checked fusedMap2245_checked
    DegreeOneSmallComparisons.comparison2245
#print axioms sourceMap2245_checked
#print axioms fusedMap2245_checked
#print axioms certified2245
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
