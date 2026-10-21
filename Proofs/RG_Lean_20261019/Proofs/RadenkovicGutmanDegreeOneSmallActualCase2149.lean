/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2149 : Family 10 := level10.get ⟨603,by decide⟩
def sourceMap2149 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,6,0,1,2,3,4,5,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2149 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2149_checked : acceptsGraphIso
    (source (graph core2149) (root 10) 0 0) DegreeOneSmallSpectrum1175.graph sourceMap2149=true := by decide +kernel
theorem fusedMap2149_checked : acceptsGraphIso
    (fused (graph core2149) (root 10) 0 0) DegreeOneSmallSpectrum1174.graph fusedMap2149=true := by decide +kernel
theorem certified2149 : Certified (graph core2149) (root 10) 0 0 :=
  of_native_maps core2149 DegreeOneSmallSpectrum1175.graph DegreeOneSmallSpectrum1174.graph
    sourceMap2149 fusedMap2149 sourceMap2149_checked fusedMap2149_checked
    DegreeOneSmallComparisons.comparison2149
#print axioms sourceMap2149_checked
#print axioms fusedMap2149_checked
#print axioms certified2149
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
