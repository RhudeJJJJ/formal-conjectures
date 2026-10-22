/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons99
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4981 : Family 10 := level10.get ⟨1576,by decide⟩
def sourceMap4981 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4981 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4981_checked : acceptsGraphIso
    (source (graph core4981) (root 10) 2 2) DegreeTwoThreeSpectrum7582.graph sourceMap4981=true := by decide +kernel
theorem fusedMap4981_checked : acceptsGraphIso
    (fused (graph core4981) (root 10) 2 2) DegreeTwoThreeSpectrum6056.graph fusedMap4981=true := by decide +kernel
theorem certified4981 : Certified (graph core4981) (root 10) 2 2 :=
  of_native_maps core4981 DegreeTwoThreeSpectrum7582.graph DegreeTwoThreeSpectrum6056.graph
    sourceMap4981 fusedMap4981 sourceMap4981_checked fusedMap4981_checked
    DegreeTwoThreeFiniteComparisons.comparison4981
#print axioms sourceMap4981_checked
#print axioms fusedMap4981_checked
#print axioms certified4981
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
