/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4576 : Family 10 := level10.get ⟨528,by decide⟩
def sourceMap4576 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4576 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4576_checked : acceptsGraphIso
    (source (graph core4576) (root 10) 2 2) DegreeTwoThreeSpectrum7138.graph sourceMap4576=true := by decide +kernel
theorem fusedMap4576_checked : acceptsGraphIso
    (fused (graph core4576) (root 10) 2 2) DegreeTwoThreeSpectrum5172.graph fusedMap4576=true := by decide +kernel
theorem certified4576 : Certified (graph core4576) (root 10) 2 2 :=
  of_native_maps core4576 DegreeTwoThreeSpectrum7138.graph DegreeTwoThreeSpectrum5172.graph
    sourceMap4576 fusedMap4576 sourceMap4576_checked fusedMap4576_checked
    DegreeTwoThreeFiniteComparisons.comparison4576
#print axioms sourceMap4576_checked
#print axioms fusedMap4576_checked
#print axioms certified4576
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
