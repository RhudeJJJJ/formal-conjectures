/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2321 : Family 10 := level10.get ⟨1013,by decide⟩
def sourceMap2321 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2321 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2321_checked : acceptsGraphIso
    (source (graph core2321) (root 10) 0 0) DegreeOneSmallSpectrum1573.graph sourceMap2321=true := by decide +kernel
theorem fusedMap2321_checked : acceptsGraphIso
    (fused (graph core2321) (root 10) 0 0) DegreeOneSmallSpectrum1577.graph fusedMap2321=true := by decide +kernel
theorem certified2321 : Certified (graph core2321) (root 10) 0 0 :=
  of_native_maps core2321 DegreeOneSmallSpectrum1573.graph DegreeOneSmallSpectrum1577.graph
    sourceMap2321 fusedMap2321 sourceMap2321_checked fusedMap2321_checked
    DegreeOneSmallComparisons.comparison2321
#print axioms sourceMap2321_checked
#print axioms fusedMap2321_checked
#print axioms certified2321
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
