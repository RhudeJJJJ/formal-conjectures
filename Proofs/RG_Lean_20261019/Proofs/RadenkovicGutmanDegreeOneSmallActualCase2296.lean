/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2296 : Family 10 := level10.get ⟨929,by decide⟩
def sourceMap2296 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,0,9,10,11,12,1,2,3,4,8,6,7] (sourceLabel 10 0 0 v)
def fusedMap2296 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,9,10,11,12,1,2,3,4,8,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2296_checked : acceptsGraphIso
    (source (graph core2296) (root 10) 0 0) DegreeOneSmallSpectrum1191.graph sourceMap2296=true := by decide +kernel
theorem fusedMap2296_checked : acceptsGraphIso
    (fused (graph core2296) (root 10) 0 0) DegreeOneSmallSpectrum1185.graph fusedMap2296=true := by decide +kernel
theorem certified2296 : Certified (graph core2296) (root 10) 0 0 :=
  of_native_maps core2296 DegreeOneSmallSpectrum1191.graph DegreeOneSmallSpectrum1185.graph
    sourceMap2296 fusedMap2296 sourceMap2296_checked fusedMap2296_checked
    DegreeOneSmallComparisons.comparison2296
#print axioms sourceMap2296_checked
#print axioms fusedMap2296_checked
#print axioms certified2296
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
