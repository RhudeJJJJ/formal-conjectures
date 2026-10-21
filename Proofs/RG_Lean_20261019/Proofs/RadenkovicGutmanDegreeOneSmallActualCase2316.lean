/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2316 : Family 10 := level10.get ⟨1004,by decide⟩
def sourceMap2316 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (sourceLabel 10 0 0 v)
def fusedMap2316 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2316_checked : acceptsGraphIso
    (source (graph core2316) (root 10) 0 0) DegreeOneSmallSpectrum1547.graph sourceMap2316=true := by decide +kernel
theorem fusedMap2316_checked : acceptsGraphIso
    (fused (graph core2316) (root 10) 0 0) DegreeOneSmallSpectrum1553.graph fusedMap2316=true := by decide +kernel
theorem certified2316 : Certified (graph core2316) (root 10) 0 0 :=
  of_native_maps core2316 DegreeOneSmallSpectrum1547.graph DegreeOneSmallSpectrum1553.graph
    sourceMap2316 fusedMap2316 sourceMap2316_checked fusedMap2316_checked
    DegreeOneSmallComparisons.comparison2316
#print axioms sourceMap2316_checked
#print axioms fusedMap2316_checked
#print axioms certified2316
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
