/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4761 : Family 10 := level10.get ⟨1029,by decide⟩
def sourceMap4761 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,14,15,16,8,9,10,11,12,13] (sourceLabel 10 2 2 v)
def fusedMap4761 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4761_checked : acceptsGraphIso
    (source (graph core4761) (root 10) 2 2) DegreeTwoThreeSpectrum7106.graph sourceMap4761=true := by decide +kernel
theorem fusedMap4761_checked : acceptsGraphIso
    (fused (graph core4761) (root 10) 2 2) DegreeTwoThreeSpectrum6040.graph fusedMap4761=true := by decide +kernel
theorem certified4761 : Certified (graph core4761) (root 10) 2 2 :=
  of_native_maps core4761 DegreeTwoThreeSpectrum7106.graph DegreeTwoThreeSpectrum6040.graph
    sourceMap4761 fusedMap4761 sourceMap4761_checked fusedMap4761_checked
    DegreeTwoThreeFiniteComparisons.comparison4761
#print axioms sourceMap4761_checked
#print axioms fusedMap4761_checked
#print axioms certified4761
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
