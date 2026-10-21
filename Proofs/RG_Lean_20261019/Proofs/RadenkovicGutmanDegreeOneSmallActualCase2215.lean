/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons44
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2215 : Family 10 := level10.get ⟨740,by decide⟩
def sourceMap2215 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2215 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2215_checked : acceptsGraphIso
    (source (graph core2215) (root 10) 0 0) DegreeOneSmallSpectrum1867.graph sourceMap2215=true := by decide +kernel
theorem fusedMap2215_checked : acceptsGraphIso
    (fused (graph core2215) (root 10) 0 0) DegreeOneSmallSpectrum1367.graph fusedMap2215=true := by decide +kernel
theorem certified2215 : Certified (graph core2215) (root 10) 0 0 :=
  of_native_maps core2215 DegreeOneSmallSpectrum1867.graph DegreeOneSmallSpectrum1367.graph
    sourceMap2215 fusedMap2215 sourceMap2215_checked fusedMap2215_checked
    DegreeOneSmallComparisons.comparison2215
#print axioms sourceMap2215_checked
#print axioms fusedMap2215_checked
#print axioms certified2215
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
