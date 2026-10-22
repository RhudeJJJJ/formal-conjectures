/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons93
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4683 : Family 10 := level10.get ⟨833,by decide⟩
def sourceMap4683 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4683 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4683_checked : acceptsGraphIso
    (source (graph core4683) (root 10) 2 2) DegreeTwoThreeSpectrum7519.graph sourceMap4683=true := by decide +kernel
theorem fusedMap4683_checked : acceptsGraphIso
    (fused (graph core4683) (root 10) 2 2) DegreeTwoThreeSpectrum5657.graph fusedMap4683=true := by decide +kernel
theorem certified4683 : Certified (graph core4683) (root 10) 2 2 :=
  of_native_maps core4683 DegreeTwoThreeSpectrum7519.graph DegreeTwoThreeSpectrum5657.graph
    sourceMap4683 fusedMap4683 sourceMap4683_checked fusedMap4683_checked
    DegreeTwoThreeFiniteComparisons.comparison4683
#print axioms sourceMap4683_checked
#print axioms fusedMap4683_checked
#print axioms certified4683
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
