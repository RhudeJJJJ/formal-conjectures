/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2099 : Family 10 := level10.get ⟨518,by decide⟩
def sourceMap2099 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2099 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2099_checked : acceptsGraphIso
    (source (graph core2099) (root 10) 0 0) DegreeOneSmallSpectrum1633.graph sourceMap2099=true := by decide +kernel
theorem fusedMap2099_checked : acceptsGraphIso
    (fused (graph core2099) (root 10) 0 0) DegreeOneSmallSpectrum1011.graph fusedMap2099=true := by decide +kernel
theorem certified2099 : Certified (graph core2099) (root 10) 0 0 :=
  of_native_maps core2099 DegreeOneSmallSpectrum1633.graph DegreeOneSmallSpectrum1011.graph
    sourceMap2099 fusedMap2099 sourceMap2099_checked fusedMap2099_checked
    DegreeOneSmallComparisons.comparison2099
#print axioms sourceMap2099_checked
#print axioms fusedMap2099_checked
#print axioms certified2099
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
