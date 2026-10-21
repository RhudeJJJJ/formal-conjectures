/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2445 : Family 10 := level10.get ⟨1417,by decide⟩
def sourceMap2445 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,10,11,12,1,2,3,4,5,6,8,9] (sourceLabel 10 0 0 v)
def fusedMap2445 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2445_checked : acceptsGraphIso
    (source (graph core2445) (root 10) 0 0) DegreeOneSmallSpectrum1532.graph sourceMap2445=true := by decide +kernel
theorem fusedMap2445_checked : acceptsGraphIso
    (fused (graph core2445) (root 10) 0 0) DegreeOneSmallSpectrum1976.graph fusedMap2445=true := by decide +kernel
theorem certified2445 : Certified (graph core2445) (root 10) 0 0 :=
  of_native_maps core2445 DegreeOneSmallSpectrum1532.graph DegreeOneSmallSpectrum1976.graph
    sourceMap2445 fusedMap2445 sourceMap2445_checked fusedMap2445_checked
    DegreeOneSmallComparisons.comparison2445
#print axioms sourceMap2445_checked
#print axioms fusedMap2445_checked
#print axioms certified2445
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
