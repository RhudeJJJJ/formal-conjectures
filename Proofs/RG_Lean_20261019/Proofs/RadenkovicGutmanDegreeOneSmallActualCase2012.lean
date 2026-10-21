/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2012 : Family 10 := level10.get ⟨350,by decide⟩
def sourceMap2012 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2012 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,10,11,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2012_checked : acceptsGraphIso
    (source (graph core2012) (root 10) 0 0) DegreeOneSmallSpectrum1099.graph sourceMap2012=true := by decide +kernel
theorem fusedMap2012_checked : acceptsGraphIso
    (fused (graph core2012) (root 10) 0 0) DegreeOneSmallSpectrum1446.graph fusedMap2012=true := by decide +kernel
theorem certified2012 : Certified (graph core2012) (root 10) 0 0 :=
  of_native_maps core2012 DegreeOneSmallSpectrum1099.graph DegreeOneSmallSpectrum1446.graph
    sourceMap2012 fusedMap2012 sourceMap2012_checked fusedMap2012_checked
    DegreeOneSmallComparisons.comparison2012
#print axioms sourceMap2012_checked
#print axioms fusedMap2012_checked
#print axioms certified2012
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
