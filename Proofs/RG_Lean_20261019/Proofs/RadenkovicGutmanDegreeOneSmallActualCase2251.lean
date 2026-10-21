/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2251 : Family 10 := level10.get ⟨809,by decide⟩
def sourceMap2251 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2251 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,5,0,1,2,3,4,9,10,11,12,7,8] (fusedLabel 10 0 0 v)
theorem sourceMap2251_checked : acceptsGraphIso
    (source (graph core2251) (root 10) 0 0) DegreeOneSmallSpectrum1742.graph sourceMap2251=true := by decide +kernel
theorem fusedMap2251_checked : acceptsGraphIso
    (fused (graph core2251) (root 10) 0 0) DegreeOneSmallSpectrum1444.graph fusedMap2251=true := by decide +kernel
theorem certified2251 : Certified (graph core2251) (root 10) 0 0 :=
  of_native_maps core2251 DegreeOneSmallSpectrum1742.graph DegreeOneSmallSpectrum1444.graph
    sourceMap2251 fusedMap2251 sourceMap2251_checked fusedMap2251_checked
    DegreeOneSmallComparisons.comparison2251
#print axioms sourceMap2251_checked
#print axioms fusedMap2251_checked
#print axioms certified2251
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
