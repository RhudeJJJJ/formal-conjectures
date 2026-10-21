/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons41
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2082 : Family 10 := level10.get ⟨476,by decide⟩
def sourceMap2082 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (sourceLabel 10 0 0 v)
def fusedMap2082 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,9,10,11,12,5,6,7,8,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap2082_checked : acceptsGraphIso
    (source (graph core2082) (root 10) 0 0) DegreeOneSmallSpectrum1090.graph sourceMap2082=true := by decide +kernel
theorem fusedMap2082_checked : acceptsGraphIso
    (fused (graph core2082) (root 10) 0 0) DegreeOneSmallSpectrum1481.graph fusedMap2082=true := by decide +kernel
theorem certified2082 : Certified (graph core2082) (root 10) 0 0 :=
  of_native_maps core2082 DegreeOneSmallSpectrum1090.graph DegreeOneSmallSpectrum1481.graph
    sourceMap2082 fusedMap2082 sourceMap2082_checked fusedMap2082_checked
    DegreeOneSmallComparisons.comparison2082
#print axioms sourceMap2082_checked
#print axioms fusedMap2082_checked
#print axioms certified2082
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
