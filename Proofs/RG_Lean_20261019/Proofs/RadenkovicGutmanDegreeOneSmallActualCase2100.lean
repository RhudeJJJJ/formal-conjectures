/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2100 : Family 10 := level10.get ⟨519,by decide⟩
def sourceMap2100 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2100 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2100_checked : acceptsGraphIso
    (source (graph core2100) (root 10) 0 0) DegreeOneSmallSpectrum1632.graph sourceMap2100=true := by decide +kernel
theorem fusedMap2100_checked : acceptsGraphIso
    (fused (graph core2100) (root 10) 0 0) DegreeOneSmallSpectrum1014.graph fusedMap2100=true := by decide +kernel
theorem certified2100 : Certified (graph core2100) (root 10) 0 0 :=
  of_native_maps core2100 DegreeOneSmallSpectrum1632.graph DegreeOneSmallSpectrum1014.graph
    sourceMap2100 fusedMap2100 sourceMap2100_checked fusedMap2100_checked
    DegreeOneSmallComparisons.comparison2100
#print axioms sourceMap2100_checked
#print axioms fusedMap2100_checked
#print axioms certified2100
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
