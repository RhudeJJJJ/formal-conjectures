/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2010 : Family 10 := level10.get ⟨347,by decide⟩
def sourceMap2010 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2010 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2010_checked : acceptsGraphIso
    (source (graph core2010) (root 10) 0 0) DegreeOneSmallSpectrum1214.graph sourceMap2010=true := by decide +kernel
theorem fusedMap2010_checked : acceptsGraphIso
    (fused (graph core2010) (root 10) 0 0) DegreeOneSmallSpectrum1455.graph fusedMap2010=true := by decide +kernel
theorem certified2010 : Certified (graph core2010) (root 10) 0 0 :=
  of_native_maps core2010 DegreeOneSmallSpectrum1214.graph DegreeOneSmallSpectrum1455.graph
    sourceMap2010 fusedMap2010 sourceMap2010_checked fusedMap2010_checked
    DegreeOneSmallComparisons.comparison2010
#print axioms sourceMap2010_checked
#print axioms fusedMap2010_checked
#print axioms certified2010
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
