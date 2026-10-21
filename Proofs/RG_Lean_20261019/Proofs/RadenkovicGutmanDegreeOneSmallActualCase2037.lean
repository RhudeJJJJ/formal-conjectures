/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2037 : Family 10 := level10.get ⟨394,by decide⟩
def sourceMap2037 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2037 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2037_checked : acceptsGraphIso
    (source (graph core2037) (root 10) 0 0) DegreeOneSmallSpectrum1209.graph sourceMap2037=true := by decide +kernel
theorem fusedMap2037_checked : acceptsGraphIso
    (fused (graph core2037) (root 10) 0 0) DegreeOneSmallSpectrum1500.graph fusedMap2037=true := by decide +kernel
theorem certified2037 : Certified (graph core2037) (root 10) 0 0 :=
  of_native_maps core2037 DegreeOneSmallSpectrum1209.graph DegreeOneSmallSpectrum1500.graph
    sourceMap2037 fusedMap2037 sourceMap2037_checked fusedMap2037_checked
    DegreeOneSmallComparisons.comparison2037
#print axioms sourceMap2037_checked
#print axioms fusedMap2037_checked
#print axioms certified2037
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
