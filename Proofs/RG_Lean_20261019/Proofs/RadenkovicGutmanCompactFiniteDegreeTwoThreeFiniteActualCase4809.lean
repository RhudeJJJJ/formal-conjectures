/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons96
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4809 : Family 10 := level10.get ⟨1156,by decide⟩
def sourceMap4809 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![8,0,1,2,3,4,5,6,7,15,16,9,10,11,12,13,14] (sourceLabel 10 2 2 v)
def fusedMap4809 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4809_checked : acceptsGraphIso
    (source (graph core4809) (root 10) 2 2) DegreeTwoThreeSpectrum7240.graph sourceMap4809=true := by decide +kernel
theorem fusedMap4809_checked : acceptsGraphIso
    (fused (graph core4809) (root 10) 2 2) DegreeTwoThreeSpectrum6298.graph fusedMap4809=true := by decide +kernel
theorem certified4809 : Certified (graph core4809) (root 10) 2 2 :=
  of_native_maps core4809 DegreeTwoThreeSpectrum7240.graph DegreeTwoThreeSpectrum6298.graph
    sourceMap4809 fusedMap4809 sourceMap4809_checked fusedMap4809_checked
    DegreeTwoThreeFiniteComparisons.comparison4809
#print axioms sourceMap4809_checked
#print axioms fusedMap4809_checked
#print axioms certified4809
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
