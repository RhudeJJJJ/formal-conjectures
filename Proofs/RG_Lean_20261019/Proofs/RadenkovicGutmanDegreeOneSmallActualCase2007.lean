/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2007 : Family 10 := level10.get ⟨343,by decide⟩
def sourceMap2007 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2007 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2007_checked : acceptsGraphIso
    (source (graph core2007) (root 10) 0 0) DegreeOneSmallSpectrum1193.graph sourceMap2007=true := by decide +kernel
theorem fusedMap2007_checked : acceptsGraphIso
    (fused (graph core2007) (root 10) 0 0) DegreeOneSmallSpectrum1453.graph fusedMap2007=true := by decide +kernel
theorem certified2007 : Certified (graph core2007) (root 10) 0 0 :=
  of_native_maps core2007 DegreeOneSmallSpectrum1193.graph DegreeOneSmallSpectrum1453.graph
    sourceMap2007 fusedMap2007 sourceMap2007_checked fusedMap2007_checked
    DegreeOneSmallComparisons.comparison2007
#print axioms sourceMap2007_checked
#print axioms fusedMap2007_checked
#print axioms certified2007
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
