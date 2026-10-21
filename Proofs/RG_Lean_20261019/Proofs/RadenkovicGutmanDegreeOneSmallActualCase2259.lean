/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons45
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2259 : Family 10 := level10.get ⟨840,by decide⟩
def sourceMap2259 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2259 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2259_checked : acceptsGraphIso
    (source (graph core2259) (root 10) 0 0) DegreeOneSmallSpectrum1879.graph sourceMap2259=true := by decide +kernel
theorem fusedMap2259_checked : acceptsGraphIso
    (fused (graph core2259) (root 10) 0 0) DegreeOneSmallSpectrum1465.graph fusedMap2259=true := by decide +kernel
theorem certified2259 : Certified (graph core2259) (root 10) 0 0 :=
  of_native_maps core2259 DegreeOneSmallSpectrum1879.graph DegreeOneSmallSpectrum1465.graph
    sourceMap2259 fusedMap2259 sourceMap2259_checked fusedMap2259_checked
    DegreeOneSmallComparisons.comparison2259
#print axioms sourceMap2259_checked
#print axioms fusedMap2259_checked
#print axioms certified2259
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
