/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4712 : Family 10 := level10.get ⟨910,by decide⟩
def sourceMap4712 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,10,11,12,13,14,15,16,8,9,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4712 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4712_checked : acceptsGraphIso
    (source (graph core4712) (root 10) 2 2) DegreeTwoThreeSpectrum7513.graph sourceMap4712=true := by decide +kernel
theorem fusedMap4712_checked : acceptsGraphIso
    (fused (graph core4712) (root 10) 2 2) DegreeTwoThreeSpectrum5778.graph fusedMap4712=true := by decide +kernel
theorem certified4712 : Certified (graph core4712) (root 10) 2 2 :=
  of_native_maps core4712 DegreeTwoThreeSpectrum7513.graph DegreeTwoThreeSpectrum5778.graph
    sourceMap4712 fusedMap4712 sourceMap4712_checked fusedMap4712_checked
    DegreeTwoThreeFiniteComparisons.comparison4712
#print axioms sourceMap4712_checked
#print axioms fusedMap4712_checked
#print axioms certified4712
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
