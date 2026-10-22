/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4700 : Family 10 := level10.get ⟨880,by decide⟩
def sourceMap4700 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,9,10,11,12,13,14,15,16,8,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4700 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4700_checked : acceptsGraphIso
    (source (graph core4700) (root 10) 2 2) DegreeTwoThreeSpectrum7537.graph sourceMap4700=true := by decide +kernel
theorem fusedMap4700_checked : acceptsGraphIso
    (fused (graph core4700) (root 10) 2 2) DegreeTwoThreeSpectrum5730.graph fusedMap4700=true := by decide +kernel
theorem certified4700 : Certified (graph core4700) (root 10) 2 2 :=
  of_native_maps core4700 DegreeTwoThreeSpectrum7537.graph DegreeTwoThreeSpectrum5730.graph
    sourceMap4700 fusedMap4700 sourceMap4700_checked fusedMap4700_checked
    DegreeTwoThreeFiniteComparisons.comparison4700
#print axioms sourceMap4700_checked
#print axioms fusedMap4700_checked
#print axioms certified4700
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
