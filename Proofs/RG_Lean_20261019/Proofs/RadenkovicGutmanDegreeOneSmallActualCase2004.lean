/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2004 : Family 10 := level10.get ⟨337,by decide⟩
def sourceMap2004 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2004 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2004_checked : acceptsGraphIso
    (source (graph core2004) (root 10) 0 0) DegreeOneSmallSpectrum1107.graph sourceMap2004=true := by decide +kernel
theorem fusedMap2004_checked : acceptsGraphIso
    (fused (graph core2004) (root 10) 0 0) DegreeOneSmallSpectrum1430.graph fusedMap2004=true := by decide +kernel
theorem certified2004 : Certified (graph core2004) (root 10) 0 0 :=
  of_native_maps core2004 DegreeOneSmallSpectrum1107.graph DegreeOneSmallSpectrum1430.graph
    sourceMap2004 fusedMap2004 sourceMap2004_checked fusedMap2004_checked
    DegreeOneSmallComparisons.comparison2004
#print axioms sourceMap2004_checked
#print axioms fusedMap2004_checked
#print axioms certified2004
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
