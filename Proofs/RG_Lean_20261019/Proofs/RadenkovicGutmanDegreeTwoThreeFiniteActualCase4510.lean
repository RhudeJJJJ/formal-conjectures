/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons90
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4510 : Family 10 := level10.get ⟨321,by decide⟩
def sourceMap4510 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,7,0,1,2,3,4,5,6,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4510 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,16,9,10,11,12,13,14] (fusedLabel 10 2 2 v)
theorem sourceMap4510_checked : acceptsGraphIso
    (source (graph core4510) (root 10) 2 2) DegreeTwoThreeSpectrum6668.graph sourceMap4510=true := by decide +kernel
theorem fusedMap4510_checked : acceptsGraphIso
    (fused (graph core4510) (root 10) 2 2) DegreeTwoThreeSpectrum5538.graph fusedMap4510=true := by decide +kernel
theorem certified4510 : Certified (graph core4510) (root 10) 2 2 :=
  of_native_maps core4510 DegreeTwoThreeSpectrum6668.graph DegreeTwoThreeSpectrum5538.graph
    sourceMap4510 fusedMap4510 sourceMap4510_checked fusedMap4510_checked
    DegreeTwoThreeFiniteComparisons.comparison4510
#print axioms sourceMap4510_checked
#print axioms fusedMap4510_checked
#print axioms certified4510
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
