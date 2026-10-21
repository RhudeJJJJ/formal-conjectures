/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2166 : Family 10 := level10.get ⟨634,by decide⟩
def sourceMap2166 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap2166 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2166_checked : acceptsGraphIso
    (source (graph core2166) (root 10) 0 0) DegreeOneSmallSpectrum1816.graph sourceMap2166=true := by decide +kernel
theorem fusedMap2166_checked : acceptsGraphIso
    (fused (graph core2166) (root 10) 0 0) DegreeOneSmallSpectrum1215.graph fusedMap2166=true := by decide +kernel
theorem certified2166 : Certified (graph core2166) (root 10) 0 0 :=
  of_native_maps core2166 DegreeOneSmallSpectrum1816.graph DegreeOneSmallSpectrum1215.graph
    sourceMap2166 fusedMap2166 sourceMap2166_checked fusedMap2166_checked
    DegreeOneSmallComparisons.comparison2166
#print axioms sourceMap2166_checked
#print axioms fusedMap2166_checked
#print axioms certified2166
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
