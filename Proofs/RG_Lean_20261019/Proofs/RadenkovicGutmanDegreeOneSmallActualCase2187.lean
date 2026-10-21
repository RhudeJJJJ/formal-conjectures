/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2187 : Family 10 := level10.get ⟨689,by decide⟩
def sourceMap2187 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2187 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2187_checked : acceptsGraphIso
    (source (graph core2187) (root 10) 0 0) DegreeOneSmallSpectrum1820.graph sourceMap2187=true := by decide +kernel
theorem fusedMap2187_checked : acceptsGraphIso
    (fused (graph core2187) (root 10) 0 0) DegreeOneSmallSpectrum1300.graph fusedMap2187=true := by decide +kernel
theorem certified2187 : Certified (graph core2187) (root 10) 0 0 :=
  of_native_maps core2187 DegreeOneSmallSpectrum1820.graph DegreeOneSmallSpectrum1300.graph
    sourceMap2187 fusedMap2187 sourceMap2187_checked fusedMap2187_checked
    DegreeOneSmallComparisons.comparison2187
#print axioms sourceMap2187_checked
#print axioms fusedMap2187_checked
#print axioms certified2187
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
