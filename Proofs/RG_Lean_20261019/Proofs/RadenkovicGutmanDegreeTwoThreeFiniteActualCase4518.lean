/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4518 : Family 10 := level10.get ⟨352,by decide⟩
def sourceMap4518 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,16,15,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4518 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (fusedLabel 10 2 2 v)
theorem sourceMap4518_checked : acceptsGraphIso
    (source (graph core4518) (root 10) 2 2) DegreeTwoThreeSpectrum6777.graph sourceMap4518=true := by decide +kernel
theorem fusedMap4518_checked : acceptsGraphIso
    (fused (graph core4518) (root 10) 2 2) DegreeTwoThreeSpectrum5625.graph fusedMap4518=true := by decide +kernel
theorem certified4518 : Certified (graph core4518) (root 10) 2 2 :=
  of_native_maps core4518 DegreeTwoThreeSpectrum6777.graph DegreeTwoThreeSpectrum5625.graph
    sourceMap4518 fusedMap4518 sourceMap4518_checked fusedMap4518_checked
    DegreeTwoThreeFiniteComparisons.comparison4518
#print axioms sourceMap4518_checked
#print axioms fusedMap4518_checked
#print axioms certified4518
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
