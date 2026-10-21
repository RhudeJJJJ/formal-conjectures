/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2009 : Family 10 := level10.get ⟨345,by decide⟩
def sourceMap2009 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,6,7,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2009 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2009_checked : acceptsGraphIso
    (source (graph core2009) (root 10) 0 0) DegreeOneSmallSpectrum1140.graph sourceMap2009=true := by decide +kernel
theorem fusedMap2009_checked : acceptsGraphIso
    (fused (graph core2009) (root 10) 0 0) DegreeOneSmallSpectrum1450.graph fusedMap2009=true := by decide +kernel
theorem certified2009 : Certified (graph core2009) (root 10) 0 0 :=
  of_native_maps core2009 DegreeOneSmallSpectrum1140.graph DegreeOneSmallSpectrum1450.graph
    sourceMap2009 fusedMap2009 sourceMap2009_checked fusedMap2009_checked
    DegreeOneSmallComparisons.comparison2009
#print axioms sourceMap2009_checked
#print axioms fusedMap2009_checked
#print axioms certified2009
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
