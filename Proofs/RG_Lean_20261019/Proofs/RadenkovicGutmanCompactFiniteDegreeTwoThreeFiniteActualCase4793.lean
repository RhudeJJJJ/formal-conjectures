/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4793 : Family 10 := level10.get ⟨1117,by decide⟩
def sourceMap4793 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4793 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4793_checked : acceptsGraphIso
    (source (graph core4793) (root 10) 2 2) DegreeTwoThreeSpectrum7199.graph sourceMap4793=true := by decide +kernel
theorem fusedMap4793_checked : acceptsGraphIso
    (fused (graph core4793) (root 10) 2 2) DegreeTwoThreeSpectrum6222.graph fusedMap4793=true := by decide +kernel
theorem certified4793 : Certified (graph core4793) (root 10) 2 2 :=
  of_native_maps core4793 DegreeTwoThreeSpectrum7199.graph DegreeTwoThreeSpectrum6222.graph
    sourceMap4793 fusedMap4793 sourceMap4793_checked fusedMap4793_checked
    DegreeTwoThreeFiniteComparisons.comparison4793
#print axioms sourceMap4793_checked
#print axioms fusedMap4793_checked
#print axioms certified4793
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
