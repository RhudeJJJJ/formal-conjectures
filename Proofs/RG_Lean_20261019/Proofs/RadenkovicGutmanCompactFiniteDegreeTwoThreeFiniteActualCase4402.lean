/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons88
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4402 : Family 9 := level9.get ⟨601,by decide⟩
def sourceMap4402 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,15,9,10,11,12,13,14] (sourceLabel 9 2 2 v)
def fusedMap4402 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4402_checked : acceptsGraphIso
    (source (graph core4402) (root 9) 2 2) DegreeTwoThreeSpectrum4929.graph sourceMap4402=true := by decide +kernel
theorem fusedMap4402_checked : acceptsGraphIso
    (fused (graph core4402) (root 9) 2 2) DegreeTwoThreeSpectrum4286.graph fusedMap4402=true := by decide +kernel
theorem certified4402 : Certified (graph core4402) (root 9) 2 2 :=
  of_native_maps core4402 DegreeTwoThreeSpectrum4929.graph DegreeTwoThreeSpectrum4286.graph
    sourceMap4402 fusedMap4402 sourceMap4402_checked fusedMap4402_checked
    DegreeTwoThreeFiniteComparisons.comparison4402
#print axioms sourceMap4402_checked
#print axioms fusedMap4402_checked
#print axioms certified4402
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
